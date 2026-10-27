module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42ThreeA7Fusion
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42ThreeA7Bound

public section

namespace CFSG.QuasithinUnique.Bridge.ThreeA7Excl

open CFSG.Quasithin CFSG.QuasithinUnique.Setup.X1 CFSG.QuasithinUnique.Setup.Family Equiv
  Equiv.Perm

def cycle5 : Perm (Fin 7) := swap 0 1 * swap 1 2 * swap 2 3 * swap 3 4

def fusion5 : Perm (Fin 7) := swap 1 2 * swap 2 4 * swap 4 3 * swap 5 6

theorem cycle5_sign : sign cycle5 = 1 := by decide +kernel

theorem fusion5_sign : sign fusion5 = 1 := by decide +kernel

theorem cycle5_pow : cycle5 ^ 5 = 1 := by decide +kernel

theorem cycle5_ne : cycle5 ≠ 1 := by decide +kernel

theorem fusion5_conj : fusion5 * cycle5 * fusion5⁻¹ = cycle5 ^ 2 := by decide +kernel

theorem exists_fusion_pair {L A : Type*} [Group L] [Group A] (π : L →* A)
    (hπ : Function.Surjective π) (hker : ∀ g : L, π g = 1 → g ∈ Subgroup.center L)
    (hZ3 : ∀ g ∈ Subgroup.center L, g ^ 3 = 1) {xb yb : A} (hx5 : xb ^ 5 = 1) (hx1 : xb ≠ 1)
    (hyx : yb * xb * yb⁻¹ = xb ^ 2) :
    ∃ x y : L, x ^ 5 = 1 ∧ x ≠ 1 ∧ y * x * y⁻¹ = x ^ 2 := by
  obtain ⟨x₁, hx₁⟩ := hπ xb
  obtain ⟨y, hy⟩ := hπ yb
  have hc5 : x₁ ^ 5 ∈ Subgroup.center L := hker _ (by rw [map_pow, hx₁, hx5])
  have hc53 : (x₁ ^ 5) ^ 3 = 1 := hZ3 _ hc5
  have hx5' : (x₁ ^ 6) ^ 5 = 1 := by
    calc (x₁ ^ 6) ^ 5 = ((x₁ ^ 5) ^ 3) ^ 2 := by rw [← pow_mul, ← pow_mul, ← pow_mul]
      _ = 1 := by rw [hc53, one_pow]
  have hπx : π (x₁ ^ 6) = xb := by
    rw [map_pow, hx₁, show 6 = 5 + 1 from rfl, pow_add, hx5, one_mul, pow_one]
  refine ⟨x₁ ^ 6, y, hx5', fun h => hx1 (by rw [← hπx, h, map_one]), ?_⟩
  generalize x₁ ^ 6 = x at hx5' hπx
  have hcc : (x ^ 2)⁻¹ * (y * x * y⁻¹) ∈ Subgroup.center L := by
    refine hker _ ?_
    rw [map_mul, map_inv, map_mul, map_mul, map_inv, map_pow, hπx, hy, hyx, inv_mul_cancel]
  generalize hc : (x ^ 2)⁻¹ * (y * x * y⁻¹) = c at hcc
  have hxc : y * x * y⁻¹ = x ^ 2 * c := by rw [← hc]; group
  have hc3 : c ^ 3 = 1 := hZ3 _ hcc
  have h5 : c ^ 5 = 1 := by
    have h1 : (y * x * y⁻¹) ^ 5 = 1 := by rw [conj_pow, hx5', mul_one, mul_inv_cancel]
    have hcomm : Commute (x ^ 2) c := Subgroup.mem_center_iff.1 hcc (x ^ 2)
    have hx10 : (x ^ 2) ^ 5 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hx5', one_pow]
    rw [hxc, hcomm.mul_pow, hx10, one_mul] at h1
    exact h1
  have hc1 : c = 1 := by
    have h := pow_gcd_eq_one.2 ⟨h5, hc3⟩
    simpa using h
  rw [hxc, hc1, mul_one]

theorem exists_fusion_pair_alt7 {L : Type*} [Group L] (π : L →* alternatingGroup (Fin 7))
    (hπ : Function.Surjective π) (hker : ∀ g : L, π g = 1 → g ∈ Subgroup.center L)
    (hZ3 : ∀ g ∈ Subgroup.center L, g ^ 3 = 1) :
    ∃ x y : L, x ^ 5 = 1 ∧ x ≠ 1 ∧ y * x * y⁻¹ = x ^ 2 := by
  refine exists_fusion_pair π hπ hker hZ3
    (xb := ⟨cycle5, Equiv.Perm.mem_alternatingGroup.2 cycle5_sign⟩)
    (yb := ⟨fusion5, Equiv.Perm.mem_alternatingGroup.2 fusion5_sign⟩) ?_ ?_ ?_
  · exact Subtype.ext (by simpa using cycle5_pow)
  · intro h
    exact cycle5_ne (congrArg Subtype.val h)
  · exact Subtype.ext (by simpa using fusion5_conj)

theorem threeA7_core (W : Type) [CommGroup W] [Finite W] (hW : ∀ w : W, w * w = 1)
    (L E : Subgroup (MulAut W)) (hq : CFSG.IsQuasisimple ↥L) (hirr : IsIrrOn L)
    (he : Nonempty ((↥L ⧸ Subgroup.center ↥L) ≃* alternatingGroup (Fin 7)))
    (hZ : Subgroup.center ↥L ≠ ⊥) (hEN : E ≤ Subgroup.normalizer (L : Set (MulAut W)))
    (hE : E ≠ ⊥) (hel : IsElemAbelian2 E) (_hquad : IsQuadratic E) :
    Nat.card E * Nat.card (fixV E) < Nat.card W := by
  obtain ⟨e⟩ := he
  have hperf : Group.IsPerfect ↥L := hq.1
  have hL : L ≠ ⊥ := ne_bot_of_isQuasisimple hq
  have hZodd : Odd (Nat.card (Subgroup.center ↥L)) := by
    by_contra hev
    rw [Nat.not_odd_iff_even] at hev
    have h2 : 2 ∣ Nat.card (Subgroup.center ↥L) := even_iff_two_dvd.1 hev
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h2
    have hcommZ : ∀ l ∈ L, l * ((x : ↥L) : MulAut W) = ((x : ↥L) : MulAut W) * l := by
      intro l hl
      have := Subgroup.mem_center_iff.1 x.2 ⟨l, hl⟩
      exact congrArg Subtype.val this
    have hxW : orderOf ((x : ↥L) : MulAut W) = 2 := by
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hx]
    have hodd2 := odd_orderOf_of_commutes hW hirr hcommZ
    rw [hxW] at hodd2
    exact absurd hodd2 (by decide)
  have hker : (redHom L e).ker = Subgroup.center ↥L := by
    ext x
    exact redHom_eq_one_iff L e x
  have hZ3 : Nat.card (Subgroup.center ↥L) = 3 := by
    have : Group.IsPerfect ↥L := hperf
    have hcov := (CFSG.SectionRank.alternating_small_odd_cover_bound (n := 7) (by norm_num)
      (by norm_num) (redHom L e) (redHom_surjective L e) (by rw [hker])
      (by rw [hker]; exact hZodd)).2 (Or.inr rfl)
    rw [hker] at hcov
    rcases hcov with h | h
    · exact absurd (Subgroup.eq_bot_of_card_eq _ h) hZ
    · exact h
  by_contra hcon
  push Not at hcon
  have h64 := card_le_two_pow_six_of_offender hW hperf hirr hL hEN hE hel e hcon
  have hker1 : ∀ g : ↥L, redHom L e g = 1 → g ∈ Subgroup.center ↥L := fun g hg =>
    (redHom_eq_one_iff L e g).1 hg
  have hZ3' : ∀ g ∈ Subgroup.center ↥L, g ^ 3 = 1 := by
    intro g hg
    have h := pow_card_eq_one' (G := Subgroup.center ↥L) (x := ⟨g, hg⟩)
    rw [hZ3] at h
    simpa using congrArg Subtype.val h
  obtain ⟨x, y, hx5, hx1, hyx⟩ :=
    exists_fusion_pair_alt7 (redHom L e) (redHom_surjective L e) hker1 hZ3'
  have h3 : 3 ∣ Nat.card (Subgroup.center ↥L) := by rw [hZ3]
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 3 h3
  have hzW : orderOf ((z : ↥L) : MulAut W) = 3 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hz]
  have hz3 : ((z : ↥L) : MulAut W) ^ 3 = 1 := by
    rw [← hzW]
    exact pow_orderOf_eq_one _
  have hz1 : ((z : ↥L) : MulAut W) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hzW
    omega
  have hzcomm : ∀ l : ↥L, (l : MulAut W) * ((z : ↥L) : MulAut W) =
      ((z : ↥L) : MulAut W) * l := by
    intro l
    have := Subgroup.mem_center_iff.1 z.2 l
    exact congrArg Subtype.val this
  have hzf : ∀ w : W, ((z : ↥L) : MulAut W) w = w → w = 1 := by
    have hinv : ∀ g ∈ L, ∀ u ∈ fixV (Subgroup.zpowers ((z : ↥L) : MulAut W)),
        g u ∈ fixV (Subgroup.zpowers ((z : ↥L) : MulAut W)) := by
      intro g hg u hu
      rw [mem_fixV_zpowers] at hu ⊢
      have := congrArg (fun m : MulAut W => m u) (hzcomm ⟨g, hg⟩)
      simp only [MulAut.mul_apply] at this
      rw [← this, hu]
    rcases hirr.2 _ hinv with h | h
    · intro w hw
      have hmem : w ∈ fixV (Subgroup.zpowers ((z : ↥L) : MulAut W)) := mem_fixV_zpowers.2 hw
      rw [h, Subgroup.mem_bot] at hmem
      exact hmem
    · exfalso
      apply hz1
      ext w
      have hmem : w ∈ fixV (Subgroup.zpowers ((z : ↥L) : MulAut W)) := by rw [h]; trivial
      exact mem_fixV_zpowers.1 hmem
  have hx5' : (x : MulAut W) ^ 5 = 1 := by simpa using congrArg Subtype.val hx5
  have hx1' : (x : MulAut W) ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hyx' : (y : MulAut W) * (x : MulAut W) * (y : MulAut W)⁻¹ = (x : MulAut W) ^ 2 := by
    simpa using congrArg Subtype.val hyx
  have hbig := card_gt_of_fusion hW hx5' hx1' hyx' (hzcomm x).symm (hzcomm y).symm hz3 hzf
  omega

end CFSG.QuasithinUnique.Bridge.ThreeA7Excl
