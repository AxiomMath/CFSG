module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GTS8
public import Mathlib.GroupTheory.SchurZassenhaus

public section

namespace CFSG.OddStandard.SmallF3.Omega

private lemma odd_mem_of_isComplement' {C : Type*} [Group C] {N₀ H₀ : Subgroup C}
    (hN₀ : N₀ ≤ Subgroup.center C) (hcard : Nat.card N₀ = 2) (hc : N₀.IsComplement' H₀)
    {c : C} (hodd : Odd (orderOf c)) : c ∈ H₀ := by
  have hNn : N₀.Normal := ⟨fun n hn g => by
    have := Subgroup.mem_center_iff.mp (hN₀ hn) g
    rw [this, mul_inv_cancel_right]
    exact hn⟩
  have hsup : c ∈ H₀ ⊔ N₀ := by
    rw [sup_comm, hc.sup_eq_top]; exact Subgroup.mem_top c
  have hset := Subgroup.coe_mul_of_left_le_normalizer_right H₀ N₀ (by
    intro g _; exact Subgroup.normalizer_eq_top_iff.mpr hNn ▸ Subgroup.mem_top g)
  rw [← SetLike.mem_coe, hset] at hsup
  obtain ⟨h, hh, n, hn, rfl⟩ := Set.mem_mul.1 hsup
  have hnc : ∀ g : C, n * g = g * n := fun g => (Subgroup.mem_center_iff.mp (hN₀ hn) g).symm
  obtain ⟨m, hm⟩ := hodd
  have hpow : (h * n) ^ orderOf (h * n) = 1 := pow_orderOf_eq_one _
  set o := orderOf (h * n) with ho
  have hcomm : Commute h n := (hnc h).symm
  have hpow' : h ^ o * n ^ o = 1 := by
    rw [← (hcomm.mul_pow o)]; exact hpow
  have hn2 : n ^ o ∈ H₀ := by
    have : n ^ o = (h ^ o)⁻¹ := eq_inv_of_mul_eq_one_right hpow'
    rw [this]; exact H₀.inv_mem (H₀.pow_mem hh o)
  have hnN : n ^ o ∈ N₀ := N₀.pow_mem hn o
  have hbot : n ^ o = 1 := by
    have := hc.disjoint.le_bot ⟨hnN, hn2⟩
    simpa using this
  have hn1 : orderOf n ∣ 2 := by
    rw [← hcard, ← Subgroup.orderOf_mk n hn]
    exact orderOf_dvd_natCard _
  have hn3 : orderOf n ∣ o := orderOf_dvd_of_pow_eq_one hbot
  have hcop : Nat.Coprime 2 o := Nat.coprime_two_left.mpr ⟨m, hm⟩
  have hn4 : orderOf n = 1 := Nat.eq_one_of_dvd_coprimes hcop hn1 hn3
  have hn5 : n = 1 := orderOf_eq_one_iff.mp hn4
  rw [hn5, mul_one]
  exact hh

theorem l34g_not_mem_closure_odd_of_cover {X : Type} [Group X] [Finite X]
    (ρ : X →* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) (hρ : Function.Surjective ρ)
    {ζ : X} (hζ2 : orderOf ζ = 2) (hζk : ρ ζ = 1) (hζc : ∀ x : X, x * ζ = ζ * x)
    (hk : ∀ P : Subgroup X, IsPGroup 2 P → P ≤ ρ.ker → Nat.card P ≤ 2) :
    ζ ∉ Subgroup.closure {x : X | Odd (orderOf x)} := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hζsq : ζ * ζ = 1 := by
    have h := pow_orderOf_eq_one ζ
    rw [hζ2] at h
    simpa [pow_two] using h
  let R : Subgroup X := ρ.ker
  let z : R := ⟨ζ, hζk⟩
  have hz2 : orderOf z = 2 := by
    rw [← Subgroup.orderOf_coe z]
    exact hζ2
  have hzsq : z * z = 1 := by
    have h := pow_orderOf_eq_one z
    rw [hz2] at h
    simpa [pow_two] using h
  have hzne : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz2
    norm_num at hz2
  have hzc : ∀ r : R, r * z = z * r := fun r => Subtype.ext (hζc r.val)
  let Z : Subgroup R := Subgroup.zpowers z
  have hzZ : z ∈ Z := Subgroup.mem_zpowers z
  have hZcard : Nat.card Z = 2 := by
    change Nat.card (Subgroup.zpowers z) = 2
    rw [Nat.card_zpowers, hz2]
  have hZc : Z ≤ Subgroup.center R := by
    change Subgroup.zpowers z ≤ Subgroup.center R
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_center_iff.mpr hzc
  have huniq : ∀ r : R, r ∈ Z → r ≠ 1 → r = z := by
    intro r hr hrne
    obtain ⟨y, -, hyuniq⟩ := (Nat.card_eq_two_iff' (1 : Z)).mp hZcard
    have h1 : (⟨r, hr⟩ : Z) = y := hyuniq _ (by intro h; exact hrne (congrArg Subtype.val h))
    have h2 : (⟨z, hzZ⟩ : Z) = y := hyuniq _ (by intro h; exact hzne (congrArg Subtype.val h))
    exact congrArg Subtype.val (h1.trans h2.symm)
  have hZ2pg : IsPGroup 2 Z := IsPGroup.of_card (n := 1) (by rw [hZcard]; norm_num)
  obtain ⟨P, hZP⟩ := IsPGroup.exists_le_sylow hZ2pg
  have hPp : IsPGroup 2 (P.map R.subtype) := P.isPGroup'.map R.subtype
  have hPle : P.map R.subtype ≤ ρ.ker := by
    rintro y ⟨p, -, rfl⟩
    exact p.2
  have hPcard_le : Nat.card (P.map R.subtype) ≤ 2 := hk _ hPp hPle
  have hPcard : Nat.card P = 2 := by
    have h1 : Nat.card (P.map R.subtype) = Nat.card P :=
      Subgroup.card_map_of_injective R.subtype_injective
    have hle : Nat.card P ≤ 2 := by rw [← h1]; exact hPcard_le
    have hge : 2 ≤ Nat.card P := by
      have := Subgroup.card_le_of_le hZP
      rwa [hZcard] at this
    omega
  have hZPeq : Z = P := by
    apply Subgroup.eq_of_le_of_card_ge hZP
    omega
  have hZidx_odd : Odd Z.index := by
    rw [hZPeq]
    exact Nat.not_even_iff_odd.mp fun h => Sylow.not_dvd_index P (even_iff_two_dvd.mp h)
  have hcop : Nat.Coprime (Nat.card Z) Z.index := by
    rw [hZcard]
    exact Nat.coprime_two_left.mpr hZidx_odd
  haveI : Z.Normal := Subgroup.normal_of_le_center hZc
  obtain ⟨H', hH'⟩ := Subgroup.exists_right_complement'_of_coprime (N := Z) hcop
  have hH'card : Nat.card H' = Z.index := by
    have h1 : Nat.card Z * Nat.card H' = Nat.card R := hH'.card_mul_card
    have h2 : Nat.card Z * Z.index = Nat.card R := Subgroup.card_mul_index Z
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (h1.trans h2.symm)
  have hH'odd : Odd (Nat.card H') := by rw [hH'card]; exact hZidx_odd
  have hH'mem : ∀ r : R, r ∈ H' ↔ Odd (orderOf r) := by
    intro r
    constructor
    · intro hr
      exact hH'odd.of_dvd_nat (Subgroup.orderOf_dvd_natCard H' hr)
    · intro hr
      exact odd_mem_of_isComplement' hZc hZcard hH' hr
  let H : Subgroup X := H'.map R.subtype
  have hHmem : ∀ x : X, x ∈ H ↔ ρ x = 1 ∧ Odd (orderOf x) := by
    intro x
    constructor
    · intro hx
      obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hx
      exact ⟨r.2, (Subgroup.orderOf_coe r).symm ▸ (hH'mem r).mp hr⟩
    · rintro ⟨hxker, hxodd⟩
      have hxR : x ∈ R := by
        rw [show R = ρ.ker from rfl]
        exact hxker
      exact Subgroup.mem_map.mpr
        ⟨⟨x, hxR⟩, (hH'mem _).mpr ((Subgroup.orderOf_mk x hxR).symm ▸ hxodd), rfl⟩
  have hHnorm : H.Normal := by
    constructor
    intro x hx g
    rw [hHmem] at hx ⊢
    refine ⟨?_, ?_⟩
    · simp [hx.1]
    · have hconj : orderOf (g * x * g⁻¹) = orderOf x :=
        (SemiconjBy.orderOf_eq g (by show g * x = (g * x * g⁻¹) * g; group)).symm
      rw [hconj]
      exact hx.2
  have hHcard : Nat.card H = Nat.card H' := by
    change Nat.card (H'.map R.subtype) = Nat.card H'
    exact Subgroup.card_map_of_injective R.subtype_injective
  have hHodd : Odd (Nat.card H) := by rw [hHcard]; exact hH'odd
  have hζnotH : ζ ∉ H := by
    intro h
    have h' := (hHmem ζ).mp h
    rw [hζ2] at h'
    obtain ⟨k, hk⟩ := h'.2
    omega
  have hHcover : ∀ r : X, ρ r = 1 → r ∈ H ∨ ζ * r ∈ H := by
    intro r hr
    obtain ⟨⟨⟨q, hqZ⟩, o⟩, hqo, -⟩ := hH'.existsUnique (⟨r, hr⟩ : R)
    have hqoX : (q : X) * ((o : R) : X) = r := by
      have := congrArg (Subtype.val) hqo
      simpa using this
    have hoH : ((o : R) : X) ∈ H := Subgroup.mem_map.mpr ⟨(o : R), o.2, rfl⟩
    rcases eq_or_ne q 1 with hq1 | hqne
    · left
      have hqx : (q : X) = 1 := by simp [hq1]
      rw [hqx, one_mul] at hqoX
      rw [← hqoX]
      exact hoH
    · right
      have hqz : q = z := huniq q hqZ hqne
      have hqx : (q : X) = ζ := by rw [hqz]
      rw [hqx] at hqoX
      have hzr : ζ * r = ((o : R) : X) := by
        rw [← hqoX, ← mul_assoc, hζsq, one_mul]
      rw [hzr]
      exact hoH
  haveI : H.Normal := hHnorm
  let ρ' : X ⧸ H →* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3) :=
    QuotientGroup.lift H ρ (by intro x hx; exact ((hHmem x).mp hx).1)
  have hρ' : Function.Surjective ρ' := by
    intro y
    obtain ⟨x, rfl⟩ := hρ y
    exact ⟨QuotientGroup.mk x, rfl⟩
  let σ : X ⧸ H := QuotientGroup.mk ζ
  have hσ2 : σ * σ = 1 := by
    change (QuotientGroup.mk' H) ζ * (QuotientGroup.mk' H) ζ = 1
    rw [← map_mul, hζsq, map_one]
  have hσ1 : σ ≠ 1 := by
    intro h
    exact hζnotH ((QuotientGroup.eq_one_iff ζ).mp h)
  have hσc : ∀ e : X ⧸ H, e * σ = σ * e := by
    intro e
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (N := H) e
    change (QuotientGroup.mk' H) x * (QuotientGroup.mk' H) ζ =
      (QuotientGroup.mk' H) ζ * (QuotientGroup.mk' H) x
    rw [← map_mul, ← map_mul, hζc x]
  have hρ'σ : ρ' σ = 1 := by
    change ρ ζ = 1
    exact hζk
  have hker' : ∀ e : X ⧸ H, ρ' e = 1 ↔ e = 1 ∨ e = σ := by
    intro e
    obtain ⟨r, rfl⟩ := QuotientGroup.mk'_surjective (N := H) e
    have hρ'r : ρ' ((QuotientGroup.mk' H) r) = ρ r := rfl
    constructor
    · intro hr
      have hr' : ρ r = 1 := by rwa [hρ'r] at hr
      rcases hHcover r hr' with hrH | hzrH
      · left
        exact (QuotientGroup.eq_one_iff r).mpr hrH
      · right
        have hz : (QuotientGroup.mk' H) (ζ * r) = 1 :=
          (QuotientGroup.eq_one_iff (ζ * r)).mpr hzrH
        have h1 : σ * ((QuotientGroup.mk' H) r) = 1 := by
          change (QuotientGroup.mk' H) ζ * (QuotientGroup.mk' H) r = 1
          rw [← map_mul]
          exact hz
        have h2 := congrArg (fun t => σ * t) h1
        rw [mul_one] at h2
        rw [← mul_assoc, hσ2, one_mul] at h2
        exact h2
    · rintro (h | h)
      · rw [h, map_one]
      · rw [h]; exact hρ'σ
  have hS8 := l34g_not_mem_closure_odd_sl23 ρ' hρ' hσ2 hσ1 hσc hker'
  intro hζ
  have hsub : (QuotientGroup.mk' H) '' {x : X | Odd (orderOf x)} ⊆
      {e : X ⧸ H | Odd (orderOf e)} := by
    rintro _ ⟨x, hx, rfl⟩
    exact hx.of_dvd_nat (orderOf_map_dvd (QuotientGroup.mk' H) x)
  have hmem : σ ∈ Subgroup.closure ((QuotientGroup.mk' H) '' {x : X | Odd (orderOf x)}) := by
    have h1 : (QuotientGroup.mk' H) ζ ∈
        (Subgroup.closure {x : X | Odd (orderOf x)}).map (QuotientGroup.mk' H) :=
      Subgroup.mem_map.mpr ⟨ζ, hζ, rfl⟩
    rwa [MonoidHom.map_closure] at h1
  exact hS8 (Subgroup.closure_mono hsub hmem)

end CFSG.OddStandard.SmallF3.Omega
