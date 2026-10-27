module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.LThreeEpsCentL

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott

open CFSG.Open Subgroup
open CFSG.RankThree.PartTwo.Sec4 CFSG.Assembly.LowTwoRank
open CFSG.HardMathSupport.Solomon.Coordinator

variable {X : Type} [Group X] [Finite X] {L : Subgroup X} [hLn : L.Normal] {π : Bool} {p f : ℕ}
  {K : Type} [Field K] {ν : ↥(slPi π 3 (p ^ f) K) →* ↥L}

theorem mem_zpowers_of_mem_zpowers_of_ne_one {G : Type*} [Group G] {x b : G} (hx3 : x ^ 3 = 1)
    (hb : b ∈ zpowers x) (hb1 : b ≠ 1) : x ∈ zpowers b := by
  have hx1 : x ≠ 1 := fun h => hb1 (by rw [h, Subgroup.zpowers_one_eq_bot] at hb; exact hb)
  have hb3 : b ^ 3 = 1 := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx3, one_zpow]
  have hfin : (zpowers x : Set G).Finite := by
    have : IsOfFinOrder x := isOfFinOrder_iff_pow_eq_one.2 ⟨3, by norm_num, hx3⟩
    exact (this.finite_zpowers)
  haveI : Finite ↥(zpowers x) := hfin.to_subtype
  have hle : zpowers b ≤ zpowers x := zpowers_le.2 hb
  have heq : zpowers b = zpowers x := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime hx3 hx1, orderOf_eq_prime hb3 hb1]
  rw [heq]
  exact Subgroup.mem_zpowers x

theorem LModel.mem_centImage_of_pow_eq_one (M : LModel L π p f K ν)
    (hproj : ∀ s ∈ Subgroup.center ↥(slPi π 3 (p ^ f) K), ν s = 1) {x : X} {y : GL (Fin 3) K}
    (hx : IsLiftAt ν x y) {w₀ : GL (Fin 3) K} (hw₀L : w₀ ∈ slPi π 3 (p ^ f) K)
    (hcent : centMod (slPi π 3 (p ^ f) K) y =
      (slPi π 3 (p ^ f) K ⊓ centralizer ({y} : Set (GL (Fin 3) K))) ⊔ zpowers w₀)
    (hwN : ((ν ⟨w₀, hw₀L⟩ : ↥L) : X) ∈ normalizer ((centImage ν y : Subgroup X) : Set X))
    (hwA : ((ν ⟨w₀, hw₀L⟩ : ↥L) : X) ∉ centImage ν y)
    (hw3 : ((ν ⟨w₀, hw₀L⟩ : ↥L) : X) ^ 3 = 1) {m : ℕ} (hm : ¬ 3 ∣ m) {b : X} (hbL : b ∈ L)
    (hbx : b * x = x * b) (hbm : b ^ m = 1) : b ∈ centImage ν y := by
  have := M.piField.finite
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau M.piField M.modThree
  set w : X := ((ν ⟨w₀, hw₀L⟩ : ↥L) : X)
  set C := slPi π 3 (p ^ f) K ⊓ centralizer ({y} : Set (GL (Fin 3) K))
  obtain ⟨s, hs⟩ := M.surj ⟨b, hbL⟩
  have hsb : ((ν s : ↥L) : X) = b := by rw [hs]
  have h1 := hx.act s (M.conjBy hx.mem s) (M.coe_conjBy hx.mem s)
  rw [hsb, show x * b * x⁻¹ = b by rw [← hbx, mul_inv_cancel_right], ← hsb] at h1
  have h2 : ν (M.conjBy hx.mem s * s⁻¹) = 1 := by
    rw [map_mul, map_inv, ← Subtype.ext h1, mul_inv_cancel]
  have h3 := M.ker_scalar _ h2
  rw [Subgroup.coe_mul, Subgroup.coe_inv, M.coe_conjBy] at h3
  have hscm : (s : GL (Fin 3) K) ∈ centMod (slPi π 3 (p ^ f) K) y := by
    exact mem_centMod_iff_scalar.2 ⟨s.2, (y * s * y⁻¹ * (s : GL (Fin 3) K)⁻¹)⁻¹, inv_mem h3,
      by group⟩
  have hw₀C : w₀ ∈ normalizer (C : Set (GL (Fin 3) K)) := by
    have hw₀cm : w₀ ∈ centMod (slPi π 3 (p ^ f) K) y := by
      rw [hcent]
      exact le_sup_right (a := C) (Subgroup.mem_zpowers w₀)
    refine mem_normalizer_of_conj_mem fun t ht => Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · exact mul_mem (mul_mem hw₀L (Subgroup.mem_inf.1 ht).1) (inv_mem hw₀L)
    · exact mem_centralizer_singleton_iff.2 (conj_commute_of_mem_centMod hw₀cm
        (mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 ht).2))
  have hmul := Subgroup.coe_mul_of_right_le_normalizer_left C (zpowers w₀)
    (zpowers_le.2 hw₀C)
  rw [hcent] at hscm
  have hscm' : (s : GL (Fin 3) K) ∈ ((C ⊔ zpowers w₀ : Subgroup (GL (Fin 3) K)) :
      Set (GL (Fin 3) K)) := hscm
  rw [hmul] at hscm'
  obtain ⟨t, ht, u, hu, htu⟩ := hscm'
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
  have htL : t ∈ slPi π 3 (p ^ f) K := (Subgroup.mem_inf.1 ht).1
  have hbe : b = ((ν ⟨t, htL⟩ : ↥L) : X) * w ^ k := by
    rw [← hsb]
    have : s = ⟨t, htL⟩ * (⟨w₀, hw₀L⟩ : ↥(slPi π 3 (p ^ f) K)) ^ k :=
      Subtype.ext (by simp only [Subgroup.coe_mul, Subgroup.coe_zpow]; exact htu.symm)
    rw [this, map_mul, map_zpow]
    rfl
  have haA : ((ν ⟨t, htL⟩ : ↥L) : X) ∈ centImage ν y :=
    mem_centImage.2 ⟨⟨t, htL⟩, mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 ht).2, rfl⟩
  obtain ⟨a', ha', hpow⟩ := exists_pow_mul_zpow hwN haA k m
  rw [← hbe, hbm] at hpow
  have hwkm' : w ^ (k * m) = a'⁻¹ := eq_inv_of_mul_eq_one_right hpow.symm
  have hw1 : w ≠ 1 := fun h => hwA (h ▸ one_mem _)
  have hwkm1 : w ^ (k * m) = 1 := by
    by_contra hne
    apply hwA
    have h4 := mem_zpowers_of_mem_zpowers_of_ne_one hw3 (zpow_mem (Subgroup.mem_zpowers w) _) hne
    have h5 : zpowers (w ^ (k * m)) ≤ centImage ν y := by
      rw [zpowers_le, hwkm']
      exact inv_mem ha'
    exact h5 h4
  have hord : orderOf w = 3 := orderOf_eq_prime hw3 hw1
  have h3km : (3 : ℤ) ∣ k * m := by
    have := orderOf_dvd_iff_zpow_eq_one.2 hwkm1
    rwa [hord] at this
  have h3k : (3 : ℤ) ∣ k := by
    rcases Int.prime_three.dvd_or_dvd h3km with h | h
    · exact h
    · exact absurd (Int.natCast_dvd_natCast.1 h) hm
  obtain ⟨j, rfl⟩ := h3k
  rw [hbe, zpow_mul, show w ^ (3 : ℤ) = 1 by rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl,
    zpow_natCast, hw3], one_zpow, mul_one]
  exact haA

theorem LModel.pow_eq_one_of_mem_centImage (M : LModel L π p f K ν)
    (hproj : ∀ s ∈ Subgroup.center ↥(slPi π 3 (p ^ f) K), ν s = 1) {y : GL (Fin 3) K}
    (hT : IsTypeThree π (p ^ f) K y) {m : ℕ}
    (hm : Nat.card ↥(slPi π 3 (p ^ f) K ⊓ centralizer ({y} : Set (GL (Fin 3) K))) = 3 * m)
    {a : X} (ha : a ∈ centImage ν y) : a ^ m = 1 := by
  have := M.piField.finite
  haveI := hT.cyclic
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau M.piField M.modThree
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ
  set u : Kˣ := Units.mk0 τ hτ0
  have hu : (u : K) = τ := rfl
  have huS : Matrix.GeneralLinearGroup.scalar (Fin 3) u ∈ slPi π 3 (p ^ f) K :=
    scalar_mem_slPi_of_cube M.piField M.modThree hτ
  set C := slPi π 3 (p ^ f) K ⊓ centralizer ({y} : Set (GL (Fin 3) K))
  obtain ⟨s, hsy, rfl⟩ := mem_centImage.1 ha
  set t : ↥C := ⟨s, Subgroup.mem_inf.2 ⟨s.2, mem_centralizer_singleton_iff.2 hsy⟩⟩
  set ζ : ↥C := ⟨Matrix.GeneralLinearGroup.scalar (Fin 3) u, Subgroup.mem_inf.2 ⟨huS,
    mem_centralizer_singleton_iff.2 (commute_of_mem_statedScalars ⟨u, rfl⟩ y).symm⟩⟩
  have hu3 : u ^ 3 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, hu, hτ, Units.val_one])
  have hζ3 : ζ ^ 3 = 1 := Subtype.ext (by
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
    show (Matrix.GeneralLinearGroup.scalar (Fin 3) u) ^ 3 = 1
    rw [← map_pow, hu3, map_one])
  have hζ1 : ζ ≠ 1 := by
    intro h1
    have h2 : Matrix.GeneralLinearGroup.scalar (Fin 3) u = 1 := congrArg Subtype.val h1
    apply hτ1
    rw [← hu, show u = 1 from scalar_injective_three (by rw [h2, map_one]), Units.val_one]
  have htm : (t ^ m) ^ 3 = 1 := by
    rw [← pow_mul, mul_comm, ← hm]
    exact pow_card_eq_one'
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1
    (CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.mem_zpowers_of_cyclic htm
      (orderOf_eq_prime hζ3 hζ1))
  have hsc : ((s ^ m : ↥(slPi π 3 (p ^ f) K)) : GL (Fin 3) K) ∈ StatedScalars (Fin 3) K := by
    have h1 := congrArg Subtype.val hk
    simp only [SubgroupClass.coe_zpow, SubgroupClass.coe_pow] at h1
    rw [SubgroupClass.coe_pow, ← h1]
    exact zpow_mem (show Matrix.GeneralLinearGroup.scalar (Fin 3) u ∈ StatedScalars (Fin 3) K from
      ⟨u, rfl⟩) k
  rw [← Subgroup.coe_pow, ← map_pow, M.map_eq_one_of_mem_statedScalars hproj hsc,
    Subgroup.coe_one]

theorem LModel.commute_of_proj (M : LModel L π p f K ν)
    (hproj : ∀ s ∈ Subgroup.center ↥(slPi π 3 (p ^ f) K), ν s = 1) {x : X} (hxL : x ∉ L)
    (hx3 : x ^ 3 = 1) {y : GL (Fin 3) K} (hx : IsLiftAt ν x y) (hT : IsTypeThree π (p ^ f) K y) :
    ∃ v : X, v ∈ L ∧ v ^ 3 = 1 ∧ v ≠ 1 ∧ v * x = x * v ∧
      ∀ g ∈ centralizer ({x} : Set X),
        g ∈ normalizer ((zpowers v ⊔ zpowers x : Subgroup X) : Set X) → g * v * g⁻¹ = v := by
  obtain ⟨w₀, hw₀L, hw₀o, hw₀C, hcent, hC3⟩ := hT.exists_w
  have hw₀cm : w₀ ∈ centMod (slPi π 3 (p ^ f) K) y := by
    rw [hcent]
    exact le_sup_right (a := slPi π 3 (p ^ f) K ⊓ centralizer ({y} : Set (GL (Fin 3) K)))
      (Subgroup.mem_zpowers w₀)
  obtain ⟨c, hc, hyw⟩ := exists_conj_eq_scalar_mul hw₀cm
  have hcL : c ∈ slPi π 3 (p ^ f) K := by
    have h1 : c = y * w₀ * y⁻¹ * w₀⁻¹ := by rw [hyw, mul_inv_cancel_right]
    rw [h1]
    exact mul_mem (conj_mem_slPi M.hπ hx.mem hw₀L) (inv_mem hw₀L)
  set sw : ↥(slPi π 3 (p ^ f) K) := ⟨w₀, hw₀L⟩
  set sc : ↥(slPi π 3 (p ^ f) K) := ⟨c, hcL⟩
  set w : X := ((ν sw : ↥L) : X)
  have hxw : x * w * x⁻¹ = w := by
    have h := hx.act sw (sc * sw) (by simp only [Subgroup.coe_mul]; exact hyw.symm)
    rw [h, map_mul, M.map_eq_one_of_mem_statedScalars hproj (s := sc) hc, one_mul]
  have hwx : w * x = x * w := by
    calc w * x = x * w * x⁻¹ * x := by rw [hxw]
      _ = x * w := by group
  have hw₀3 : w₀ ^ 3 = 1 := by
    have := pow_orderOf_eq_one w₀
    rwa [hw₀o] at this
  have hw3 : w ^ 3 = 1 := by
    have : sw ^ 3 = 1 := Subtype.ext (by
      rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
      exact hw₀3)
    rw [← Subgroup.coe_pow, ← map_pow, this, map_one, Subgroup.coe_one]
  have hwA : w ∉ centImage ν y := M.not_mem_centImage (w := sw) hw₀C
  have hw1 : w ≠ 1 := fun h => hwA (h ▸ one_mem _)
  refine ⟨w, (ν sw).2, hw3, hw1, hwx, fun g hg hgQ => ?_⟩
  have hxN : x ∈ normalizer ((zpowers w : Subgroup X) : Set X) := by
    refine mem_normalizer_of_conj_mem fun a ha => ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    rw [← conj_zpow, hxw]
    exact Subgroup.zpow_mem_zpowers w k
  have hmul := Subgroup.coe_mul_of_right_le_normalizer_left (zpowers w) (zpowers x)
    (zpowers_le.2 hxN)
  have hgwQ : g * w * g⁻¹ ∈ ((zpowers w ⊔ zpowers x : Subgroup X) : Set X) :=
    (Subgroup.mem_normalizer_iff.1 hgQ w).1 (le_sup_left (b := zpowers x) (Subgroup.mem_zpowers w))
  rw [hmul] at hgwQ
  obtain ⟨a, ha, b, hb, hab'⟩ := hgwQ
  have hab : a * b = g * w * g⁻¹ := hab'
  have hwL : w ∈ L := (ν sw).2
  have hb1 : b = 1 := by
    by_contra hb1
    apply hxL
    have hbL : b ∈ L := by
      have h1 : b = a⁻¹ * (g * w * g⁻¹) := by rw [← hab]; group
      rw [h1]
      exact mul_mem (inv_mem ((zpowers_le.2 hwL) ha)) (hLn.conj_mem w hwL g)
    exact (zpowers_le.2 hbL) (mem_zpowers_of_mem_zpowers_of_ne_one hx3 hb hb1)
  rw [hb1, mul_one] at hab
  have hgwz : g * w * g⁻¹ ∈ zpowers w := hab ▸ ha
  rcases eq_of_mem_zpowers_of_pow_three hw3 hgwz with h | h | h
  · exfalso
    apply hw1
    calc w = g⁻¹ * (g * w * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group
  · exact h
  · exfalso
    have hwinv : g * w * g⁻¹ = w⁻¹ := by
      rw [h]
      calc w ^ 2 = w ^ 3 * w⁻¹ := by group
        _ = w⁻¹ := by rw [hw3, one_mul]
    haveI hAcyc : IsCyclic ↥(centImage ν y : Subgroup X) := isCyclic_centImage hT
    have hwN : w ∈ normalizer ((centImage ν y : Subgroup X) : Set X) :=
      mem_normalizer_of_conj_mem fun a ha => conj_mem_centImage hw₀cm ha
    obtain ⟨m, hm, -, hm3⟩ := hT.card_eq M.piField M.modThree M.two_lt
    have hgN : g ∈ normalizer ((centImage ν y : Subgroup X) : Set X) := by
      refine mem_normalizer_of_conj_mem fun a ha => ?_
      obtain ⟨haL, hax⟩ := Subgroup.mem_inf.1 (hx.centImage_le ha)
      have h1 := mem_centralizer_singleton_iff.1 hax
      have h2 := mem_centralizer_singleton_iff.1 hg
      refine M.mem_centImage_of_pow_eq_one hproj hx hw₀L hcent hwN hwA hw3 hm3
        (hLn.conj_mem a haL g) ?_ ?_
      · calc g * a * g⁻¹ * x = g * a * (g⁻¹ * x * g) * g⁻¹ := by group
          _ = g * a * x * g⁻¹ := by
              rw [show g⁻¹ * x * g = x by rw [mul_assoc, ← h2, inv_mul_cancel_left]]
          _ = g * (a * x) * g⁻¹ := by group
          _ = g * (x * a) * g⁻¹ := by rw [h1]
          _ = g * x * a * g⁻¹ := by group
          _ = x * g * a * g⁻¹ := by rw [h2]
          _ = x * (g * a * g⁻¹) := by group
      · rw [conj_pow, M.pow_eq_one_of_mem_centImage hproj hT hm ha, mul_one, mul_inv_cancel]
    have hw3' : ∀ a ∈ (centImage ν y : Subgroup X), w ^ 3 * a * (w ^ 3)⁻¹ = a := fun a _ => by
      rw [hw3, one_mul, inv_one, mul_one]
    obtain ⟨b', hb', hb''⟩ := M.exists_conj_ne (X := X) hT (w := sw) hC3
    exact false_of_conj_inv hAcyc hwN hgN hw3' ⟨b', hb', hb''⟩ fun a _ => by
      rw [hwinv, inv_inv]

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott
